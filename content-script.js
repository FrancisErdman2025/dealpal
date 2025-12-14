// content-script.js - DealPal Amazon-specific product extraction
(function() {
  function extract() {
    try {
      const title = document.querySelector('#productTitle')?.innerText?.trim() || document.title;

      // Amazon-specific price detection
      const priceEl =
        document.querySelector('#priceblock_ourprice') ||
        document.querySelector('#priceblock_dealprice') ||
        document.querySelector('#priceblock_saleprice') ||
        document.querySelector('.a-price .a-offscreen');

      const priceText = priceEl ? priceEl.innerText.trim() : null;
      const numericPrice = priceText ? parseFloat(priceText.replace(/[^\d\.]/g, '')) : null;

      const productInfo = {
        title: title || '',
        priceText: priceText || null,
        price: numericPrice,
        url: location.href,
        ts: Date.now()
      };

      chrome.runtime.sendMessage({ type: 'PRODUCT_INFO', payload: productInfo });
    } catch (e) {
      console.error('DealPal content script extract error', e);
      chrome.runtime.sendMessage({
        type: 'PRODUCT_INFO',
        payload: { title: document.title || '', url: location.href, ts: Date.now() }
      });
    }
  }

  // run immediately
  extract();
})();
